$(document).ready(function() 
{
    var page_name = window.location.hash;
    if (page_name === '#logged-out') {
        $('.flip-container').addClass('active');

    }

    setTimeout(function() {
        $('.flip-container').height(Math.max($('.back').height(), $('.front').height()) + 40);
        $('.flip-container').addClass('in');
        setTimeout(function() {
            $('.login-advertisement').addClass('in');
        }, 800);
    }, 500);

    $(window).on('resize', function() {
    	$('.flip-container').height($('.front').height() + 40);
    });

    $('.btn-primary, #btn-sidebar').on('click', function() {
        setTimeout(function() 
        {
        	$('.flip-container').height($('.front').height() + 40);
        }, 100);

    });

    $('.btn-login-again').on('click', function() {
        $('.flip-container').removeClass('active');
    });

    var checkRadioCarouselLarger = function(bgRadio){
        var currRatio = ($(window).width() / $(window).height()).toFixed(2);
        if (bgRadio < currRatio) {
            return false;
        }
        else{
            return true;
        }
    };

    var checkRadioCarousel = function(element){
        var radioChecked = checkRadioCarouselLarger(element.attr('data-ratio'));
        if(radioChecked){
            $('#xbackdrop .bgdrop-image').removeClass('height-auto-carousel');
            $('#xbackdrop .bgdrop-image').addClass('width-auto-carousel');
        }else{
            $('#xbackdrop .bgdrop-image').removeClass('width-auto-carousel');
            $('#xbackdrop .bgdrop-image').addClass('height-auto-carousel');
        }
    };

    //  Exec to fix the full screen image
    checkRadioCarousel($('#xbackdrop .bgdrop-image:first-child'));

    //  Listening the event when slide finishs changing and fix background for fullscreen.
    $('.carousel').on('slide.bs.carousel', function(objInfo) {
        
        // Show or hide background
        $('#xbackdrop .bgdrop-image').removeClass('active');
        $('.' + $(objInfo.relatedTarget).attr('data-bg') + '-image').addClass('active');

        // Fix the full screen background
        checkRadioCarousel($('.' + $(objInfo.relatedTarget).attr('data-bg') + '-image'));
    });
    $(window).on('resize', function(){
        checkRadioCarousel($('#xbackdrop .bgdrop-image:first-child'));
    });
});